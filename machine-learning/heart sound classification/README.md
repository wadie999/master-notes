
# Projet Battements Cardiaques

This project is developed at Université Toulouse III - Paul Sabatier under the guidance of Professor SANDRINE MOUYSSET. It aims to integrate machine learning techniques in the analysis of heart sounds, classifying them into three categories: normal, murmurs, and artifacts.

[Notebook](https://github.com/wadie999/master-notes/blob/main/machine-learning/heart%20sound%20classification/Projet_battements_cardiaques1(2).ipynb) + [Report](https://github.com/wadie999/master-notes/blob/main/machine-learning/heart%20sound%20classification/relatoriolab.pdf)



## Overview

The project utilizes both supervised and unsupervised machine learning methods to classify distinct types of heartbeats from audio recordings transformed into Mel Frequency Cepstral Coefficients (MFCC). The goal is to develop a robust system for medical diagnosis and patient monitoring by accurately classifying various cardiac anomalies. 



## Data Description

The dataset includes three types of heart sounds:
- **Normal:** 351 samples
- **Murmurs:** 129 samples
- **Artifacts:** 40 samples

These sounds are pre-processed using the `librosa` library to extract MFCC, facilitating feature extraction for the classification models.

## Machine Learning Methods

### Supervised Learning

We employed several machine learning models to handle labeled data:
- **Random Forest**
- **Support Vector Machines (SVM)**
- **k-Nearest Neighbors (k-NN)**

Each model is tuned and evaluated using standard metrics such as accuracy and precision, with detailed analyses provided on the impact of various hyperparameters.

### Unsupervised Learning

Unsupervised techniques were also explored to uncover hidden patterns in unlabeled data:
- **KMeans Clustering**

Data is analyzed without preprocessing, directly clustering the raw MFCC coefficients, and with preprocessing using Principal Component Analysis (PCA) to reduce dimensionality.

## Results

The models demonstrate varying degrees of success, with detailed results including confusion matrices and performance scores. Insights from both supervised and unsupervised approaches are combined to suggest optimal strategies for heartbeat classification.

## File Structure

- **data/**
  - Audio recordings of heartbeats processed into MFCC.
- **models/**
  - Trained model files.
- **notebooks/**
  - Jupyter notebooks containing exploratory data analysis and model training.

## Dependencies

Ensure you have the following Python libraries installed:
- `librosa`
- `sklearn`
- `numpy`
- `matplotlib`

## Authors

- EL AMRANI Wadie
- RATABOUIL Guilhem

## Acknowledgements

We extend our gratitude to our professor, SANDRINE MOUYSSET, for her guidance and support throughout the project.

## License

This project is licensed under the MIT License - see the [LICENSE.md](LICENSE.md) file for details.
