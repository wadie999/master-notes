
# Deep Learning Audio Classification Project

## Research Article
The findings and methodologies of this project are detailed in an accompanying research article. It provides a comprehensive analysis of the results obtained using the developed architectures and the implications for further research in audio classification [Deep Learning for Audio Classification](https://github.com/wadie999/master-notes/blob/main/audio-classification/docs/audio%20class%20paper.pdf)

## Overview
This project explores the application of deep learning techniques to classify audio files using the ESC-10 dataset. It involves developing neural network architectures from scratch using Pytorch, proving a fundamental understanding of deep learning principles and practices. The detailed code is available in the [Notebook](https://github.com/wadie999/master-notes/blob/main/audio-classification/audio%20classification.ipynb)

## Dataset
The project utilizes the [ESC-10 dataset](https://github.com/karolpiczak/ESC-10), which is a subset of the Environmental Sound Classification dataset (ESC-50). It includes labeled audio files across 10 classes, specifically designed for environmental sound classification tasks.

## Architectures
Several deep learning architectures were implemented to address the challenges of audio classification. Here is a snapshot of the `ComplexCNN` architecture used in the project, highlighting custom layer configurations and operations:

```python
import torch.nn as nn
import torch.nn.functional as F

class ComplexCNN(nn.Module):
    def __init__(self, output_size):
        super(ComplexCNN, self).__init__()
        
        self.conv1 = nn.Conv2d(in_channels=1, out_channels=32, kernel_size=3, padding=1)
        self.conv2 = nn.Conv2d(in_channels=32, out_channels=64, kernel_size=3, padding=1)
        self.conv3 = nn.Conv2d(in_channels=64, out_channels=128, kernel_size=3, padding=1)
        self.conv4 = nn.Conv2d(in_channels=128, out_channels=128, kernel_size=3, padding=1)

        self.pool = nn.MaxPool2d(kernel_size=2, stride=2)

        self.bn1 = nn.BatchNorm2d(32)
        self.bn2 = nn.BatchNorm2d(64)
        self.bn3 = nn.BatchNorm2d(128)

        self.dropout = nn.Dropout(0.5)

        self.fc1 = nn.Linear(13312, 512)
        self.fc2 = nn.Linear(512, output_size)

    def forward(self, x):
        x = self.pool(F.relu(self.bn1(self.conv1(x))))
        x = self.pool(F.relu(self.bn2(self.conv2(x))))
        x = self.pool(F.relu(self.bn3(self.conv3(x))))
        x = self.pool(F.relu(self.conv4(x)))

        x = x.view(-1, 13312)

        x = F.relu(self.fc1(x))
        x = self.dropout(x)
        x = self.fc2(x)
        return x
```

This code illustrates the detailed layer configuration and forward propagation method, providing insights into the construction and optimization of CNNs for handling audio data.

