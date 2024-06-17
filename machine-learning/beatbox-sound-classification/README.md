
# Projet Beatbox

This project, developed at Université Toulouse III - Paul Sabatier under the guidance of Professor Sandrine Mouysset, focuses on detecting and recognizing various beatbox sounds from audio recordings. Utilizing supervised and unsupervised learning methods, this project aims to accurately classify 12 distinct beatbox sounds.


[Notebook](https://github.com/wadie999/master-notes/blob/main/machine-learning/beatbox-sound-classification/ProjetBeatbox(1).ipynb) + [Report](https://github.com/wadie999/master-notes/blob/main/machine-learning/beatbox-sound-classification/projet_beatbox-5.pdf)

## Project Overview

Leveraging modern data science techniques, the project explores the potential of machine learning in the realm of audio processing. The beatbox sounds are processed into a computationally manageable form using cepstral analysis, setting the stage for sophisticated algorithmic classification.

## Data Description

The dataset comprises audio samples of 12 unique beatbox sounds, each represented in `.wav` format. These sounds are transformed into feature-rich data using Mel Frequency Cepstral Coefficients (MFCC) to facilitate effective machine learning processes.

## Machine Learning Techniques Employed

### Supervised Learning

- **Support Vector Machine (SVM)**: This model is the primary classification technique used for this project, optimized to classify multiple classes of beatbox sounds effectively.

### Unsupervised Learning

- **K-Means Clustering**: Used to explore inherent structures within the beatbox sounds without pre-labeled data. Additionally, Principal Component Analysis (PCA) is employed to tackle high dimensionality, enhancing the dataset's manageability and the model's performance.

## Methodology

1. **Data Preprocessing**: Conversion of audio files into MFCC, reducing dimensionality where necessary using PCA.
2. **Model Training**: Application of SVM for supervised learning and K-Means for unsupervised clustering.
3. **Evaluation**: Models are assessed based on accuracy metrics derived from confusion matrices and performance scores.

## Results

The project has shown promising results in the classification of beatbox sounds with detailed comparisons between the performances of supervised and unsupervised models both with and without preprocessing.

## File Structure

- **data/**: Contains the `.wav` files and their MFCC transformations.
- **models/**: Stores the trained models, including SVM and K-Means configurations.
- **notebooks/**: Jupyter notebooks detailing the processes from data preprocessing to model evaluation and testing.

## Dependencies

This project requires the following Python libraries:
- `librosa` for audio processing
- `sklearn` for machine learning algorithms
- `matplotlib` and `seaborn` for data visualization
- `numpy` for numerical operations

## Authors

- EL AMRANI Wadie
- RATABOUIL Guilhem

## Acknowledgements

We thank Professor Sandrine Mouysset for her invaluable guidance and support throughout the duration of this project.

